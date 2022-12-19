const ArgumentType = require('../../extension-support/argument-type');
const BlockType = require('../../extension-support/block-type');
const Cast = require('../../util/cast');
const formatMessage = require('format-message');
const BLE = require('../../io/ble');
const Base64Util = require('../../util/base64-util');
const MathUtil = require('../../util/math-util');
const RateLimiter = require('../../util/rateLimiter.js');
const log = require('../../util/log');

/**
 * Icon svg to be displayed at the left edge of each extension block, encoded as a data URI.
 * @type {string}
 */
// eslint-disable-next-line max-len
const iconURI = 'data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAACgAAAAoCAIAAAADnC86AAAAAXNSR0IArs4c6QAAAARnQU1BAACxjwv8YQUAAAAJcEhZcwAADsMAAA7DAcdvqGQAAAGeSURBVFhH7Zc7UsMwEEAdzhIoGE5gn4ChoeIIcss9aJw2R6BKg3UDTpChiHwXI1mr1ce7SsgMSqPXaCKt9ulrTTbzPDe34A7K4lRxMaq4GFVcDF4s+25j6SVU5Znkru8618nQdf1OThO0J+hvNckoIEAjRqjkUINoIZaiHRQEejix9QphE1I9ETU4aSuGMQhUavTjSQfPiME7uqy8GVdGhE6PlmMAVC3QYvTifBgzzja3G04d5aDEkA1y5czOm90KHxaOjhDHXrobAHM54/VzDlKsr9P09fmtC/H6bH8325e3xbw/pNdqOh2X8ulhu5Qs94927AEr8cqbM/+V4wkvdSqWH++plzerHxN7HYlYHvamiL2smVjBPOGewF5b8M61K1xDeI4uPNTkIYzE6M1wjZk41JEY2olrs0AMG1PmzG50cWIvzlxXgDJjVk7NBaD4vJdeMp9ZHwz9vfbZ9RvhH61VWie+xMuYTefsq2hpo5fLiS/z0qttsfPD02/QK2Bk4ePo1yQ8XP9IuOp6erqm/lssRhUXo4qLcSNx0/wCJgXQg+b3xr0AAAAASUVORK5CYII=';

/**
 * A list of ApitorQ BLE UUIDs.
 * @enum
 */
const ApitorQ_BleUuids = {
    UUID_SERVICE:                    '0000f0ff-0000-1000-8000-00805f9b34fb',
    UUID_CHARACTERISTIC_WRITE:       '0000f001-0000-1000-8000-00805f9b34fb',
    UUID_CHARACTERISTIC_READ_NOTIFY: '0000f002-0000-1000-8000-00805f9b34fb',
};

/**
 * Enum for LED id.
 * @readonly
 * @enum {number}
 */
const ApitorQ_LedID = {
    L1:      0x01,
    L2:      0x02,
    ALL:     0x04,
    ALLSTOP: 0x03,
};

/**
 * Enum for LED color id.
 * @readonly
 * @enum {number}
 */
const ApitorQ_LedColorID = {
    OFF:     0x00,
    RED:     0x01,
    ORANGE:  0x02,
    YELLOW:  0x03,
    GREEN:   0x04,
    CYAN:    0x05,
    BLUE:    0x06,
    PURPLE:  0x07,
};

/**
 * Enum for motor id.
 * @readonly
 * @enum {number}
 */
const ApitorQ_MotorID = {
    M1:      0x06,
    M2:      0x07,
    ALL:     0x09,
    ALLSTOP: 0x10,
};

/**
 * Enum for motor direction.
 * @readonly
 * @enum {number}
 */
const ApitorQ_MotorDirectionID = {
    D1:   0x01,
    D2:   0x02,
    STOP: 0x00,
};

/**
 * Enum for infrared sensor id.
 * @readonly
 * @enum {number}
 */
const ApitorQ_InfraredID = {
    R1:      0x00,
};

/**
 * Enum for color sensor values.
 * @readonly
 * @enum {number}
 */
const ApitorQ_SensorColorID = {
    R: 0x01,
    G: 0x02,
    B: 0x03,
    X: 0x04,
};

/**
 * A time interval to wait (in milliseconds) while a block that sends a BLE message is running.
 * @type {number}
 */
const BLESendInterval = 100;

/**
 * A maximum number of BLE message sends per second, to be enforced by the rate limiter.
 * @type {number}
 */
const BLESendRateMax = 20;

/**
 * Manage communication with a ApitorQ peripheral over a Bluetooth Low Energy client socket.
 */
class ApitorQ {

    constructor (runtime, extensionId) {

        /**
         * The Scratch 3.0 runtime used to trigger the green flag button.
         * @type {Runtime}
         * @private
         */
        this._runtime = runtime;
        this._runtime.on('PROJECT_STOP_ALL', this.stopAll.bind(this));

        /**
         * The id of the extension this peripheral belongs to.
         */
        this._extensionId = extensionId;

        /**
         * The Bluetooth connection socket for reading/writing peripheral data.
         * @type {BLE}
         * @private
         */
        this._ble = null;
        this._runtime.registerPeripheralExtension(extensionId, this);

        /**
         * A rate limiter utility, to help limit the rate at which we send BLE messages
         * over the socket to Scratch Link to a maximum number of sends per second.
         * @type {RateLimiter}
         * @private
         */
        this._rateLimiter = new RateLimiter(BLESendRateMax);

        this.reset = this.reset.bind(this);
        this._onConnect = this._onConnect.bind(this);
        this._onMessage = this._onMessage.bind(this);

        /**
         * Hardware sensors
         * @private
         */
        this._sensorColor     = 0;
        this._sensorInfrared1 = 0;
        this._sensorPower     = 0;
    }

    /**
     * @return {number} - the latest value received from the infrared1 sensor.
     */
    get sensorInfrared1 () {
        return  this._sensorInfrared1;
    }

    /**
     * @return {number} - the latest value received from the color sensor.
     */
    get sensorColor () {
        return  this._sensorColor;
    }

    /**
     * Configure ApitorQ LED to a specific color/blink.
     * @param {ApitorQ_LedID}      id      - id of led to set
     * @param {ApitorQ_LedColorID} color   - color to set
     * @param {number}             offTime - pauses between blinks; 0 to disable; measured in 0.1 sec
     * @param {number}             onTime  - blink duration; 0 to disable; measured in 0.1 sec
     * @return {Promise} - a promise of the completion of the set led send operation.
     */
    setLED (id, color, offTime, onTime) {
        if ((color == 0) && (id == ApitorQ_LedID.ALL)) {
            id = ApitorQ_LedID.ALLSTOP;
        }

        const cmd = [
            0x55, 0xaa, 0x04,
            id,
            color,
            onTime,
            offTime
        ];

        return this.send(ApitorQ_BleUuids.UUID_CHARACTERISTIC_WRITE, cmd);
    }

    /**
     * Configure ApitorQ motor.
     * @param {ApitorQ_MotorDirectionID} id    - id of motor to set
     * @param {number}                   speed - speed [-16 ... 0 ... +16]
     * @return {Promise}  - a promise of the completion of the set led send operation.
     */
    setMotor (id, speed) {
        let direction = 0;
        if (speed > 0) {
            direction = ApitorQ_MotorDirectionID.D1;
        } else if (speed == 0) {
            direction = ApitorQ_MotorDirectionID.STOP;
        } else {
            direction = ApitorQ_MotorDirectionID.D2;
            speed = -speed;
        }

        if (direction == ApitorQ_MotorDirectionID.STOP) {
            speed = 0;
        }

        if ((speed == 0) && (id == ApitorQ_MotorID.ALL)) {
            id = ApitorQ_MotorID.ALLSTOP;
        }

        const cmd = [
            0x55, 0xaa, 0x03,
            id,
            direction,
            speed
        ];

        return this.send(ApitorQ_BleUuids.UUID_CHARACTERISTIC_WRITE, cmd);
    }

    /**
     * Fully stop ApitorQ, as if no program is running.
     */
    stopAll () {
        if (!this.isConnected()) return;

        this.setMotor(ApitorQ_MotorID.ALL, 0);
        this.setLED(ApitorQ_LedID.ALL, ApitorQ_LedColorID.OFF);
    }

    /**
     * Called by the runtime when user wants to scan for a ApitorQ peripheral.
     */
    scan () {
        if (this._ble) {
            this._ble.disconnect();
        }
        this._ble = new BLE(this._runtime, this._extensionId, {
            filters: [{
                services: [ApitorQ_BleUuids.UUID_SERVICE],
                namePrefix: "ApitorTQ",
            }]
        }, this._onConnect, this.reset);
    }

    /**
     * Called by the runtime when user wants to connect to a certain peripheral.
     * @param {number} id - the id of the peripheral to connect to.
     */
    connect (id) {
        if (this._ble) {
            this._ble.connectPeripheral(id);
        }
    }

    /**
     * Disconnects from the current BLE socket.
     */
    disconnect () {
        if (this._ble) {
            this._ble.disconnect();
        }

        this.reset();
    }

    /**
     * Reset all the state and timeout/interval ids.
     */
    reset () {
        this._sensorColor     = 0;
        this._sensorInfrared1 = 0;
        this._sensorPower     = 0;
    }

    /**
     * Called by the runtime to detect whether the peripheral is connected.
     * @return {boolean} - the connected state.
     */
    isConnected () {
        let connected = false;
        if (this._ble) {
            connected = this._ble.isConnected();
        }
        return connected;
    }

    /**
     * Write a message to ApitorQ BLE socket.
     * @param {number}  uuid              - the UUID of the characteristic to write to
     * @param {Array}   message           - the message to write.
     * @param {boolean} [useLimiter=true] - if true, use the rate limiter
     * @return {Promise} - a promise result of the write operation
     */
    send (uuid, message, useLimiter = true) {
        if (!this.isConnected()) return Promise.resolve();

        if (useLimiter) {
            if (!this._rateLimiter.okayToSend()) return Promise.resolve();
        }

        return this._ble.write(
            ApitorQ_BleUuids.UUID_SERVICE,
            uuid,
            Base64Util.uint8ArrayToBase64(message),
            'base64'
        );
    }

    /**
     * Send ApitorQ connection password
     * @private
     */
    _sendPassword () {
        const password = Base64Util.base64ToUint8Array("VaoRIGR5b3pXT1BmMDUyZ1dWUDQ="); // 55aa112064796f7a574f50663035326757565034
        this.send(ApitorQ_BleUuids.UUID_CHARACTERISTIC_WRITE, password);
    }

    /**
     * Initialize after BLE has connected.
     * @private
     */
    _onConnect () {
        this._sendPassword();

        this._ble.startNotifications(
            ApitorQ_BleUuids.UUID_SERVICE,
            ApitorQ_BleUuids.UUID_CHARACTERISTIC_READ_NOTIFY,
            this._onMessage
        );
    }

    /**
     * Process the sensor data from the incoming BLE characteristic.
     * @param {object} base64 - the incoming BLE data.
     * @private
     */
    _onMessage (base64) {
        const data = Base64Util.base64ToUint8Array(base64);
        if ((data[0] != 0x55) || (data[1] != 0xaa) || (data[2] != 0x05) || data.length != 8) {
            console.log("Error: unknown message: " + data);
            return;
        }

        this._sensorColor     = data[4];
        this._sensorInfrared1 = data[5];
        this._sensorPower     = data[7];
    }
}

/**
 * Scratch 3.0 blocks to interact with a ApitorQ peripheral.
 */
class Scratch3ApitorQBlocks {

    /**
     * @return {string} - the ID of this extension.
     */
    static get EXTENSION_ID () {
        return 'apitorq';
    }

    /**
     * Construct a set of ApitorQ blocks.
     * @param {Runtime} runtime - the Scratch 3.0 runtime.
     */
    constructor (runtime) {
        /**
         * The Scratch 3.0 runtime.
         * @type {Runtime}
         */
        this.runtime = runtime;

        // Create a new ApitorQ peripheral instance
        this._peripheral = new ApitorQ(this.runtime, Scratch3ApitorQBlocks.EXTENSION_ID);
    }

    /**
     * @returns {object} metadata for this extension and its blocks.
     */
    getInfo () {
        return {
            id: Scratch3ApitorQBlocks.EXTENSION_ID,
            name: 'ApitorQ',
            blockIconURI: iconURI,
            showStatusButton: true,
            blocks: [
                {
                    opcode: 'commandMotorOff',
                    text: formatMessage({
                        id: 'apitor.commandMotorOff',
                        default: 'turn motor [MOTOR_ID] off',
                        description: 'Apitor Robot X: turn a motor off',
                    }),
                    blockType: BlockType.COMMAND,
                    arguments: {
                        MOTOR_ID: {
                            type: ArgumentType.NUMBER,
                            menu: 'MOTOR_ID',
                            defaultValue: ApitorQ_MotorID.ALL,
                        },
                    },
                },
                {
                    opcode: 'commandMotorOn',
                    text: formatMessage({
                        id: 'apitor.startMotorPower',
                        default: 'set motor [MOTOR_ID] direction [MOTOR_DIRECTION_ID] speed [MOTOR_SPEED]',
                        description: 'Apitor Robot X: set motor\'s direction and speed',
                    }),
                    blockType: BlockType.COMMAND,
                    arguments: {
                        MOTOR_ID: {
                            type: ArgumentType.NUMBER,
                            menu: 'MOTOR_ID',
                            defaultValue: ApitorQ_MotorID.ALL,
                        },
                        MOTOR_DIRECTION_ID: {
                            type: ArgumentType.NUMBER,
                            menu: 'MOTOR_DIRECTION_ID',
                            defaultValue: ApitorQ_MotorDirectionID.D1,
                        },
                        MOTOR_SPEED: {
                            type: ArgumentType.NUMBER,
                            menu: 'MOTOR_SPEED',
                            defaultValue: 1,
                        },
                    },
                },
                {
                    opcode: 'commandSetLedOn',
                    text: formatMessage({
                        id: 'apitor.commandSetLedOn',
                        default: 'set led [LED_ID] color to [LED_COLOR_ID]',
                        description: 'Apitor Robot X: set LED color',
                    }),
                    blockType: BlockType.COMMAND,
                    arguments: {
                        LED_ID: {
                            type: ArgumentType.NUMBER,
                            menu: 'LED_ID',
                            defaultValue: ApitorQ_LedID.ALL,
                        },
                        LED_COLOR_ID: {
                            type: ArgumentType.NUMBER,
                            menu: 'LED_COLOR_ID',
                            defaultValue: ApitorQ_LedColorID.RED,
                        },
                    },
                },
                {
                    opcode: 'commandSetLedBlink',
                    text: formatMessage({
                        id: 'apitor.commandSetLedBlink',
                        default: 'set led [LED_ID] color to [LED_COLOR_ID] blink [ON_TIME]/[OFF_TIME]',
                        description: 'Apitor Robot X: set LED color and blinking timings',
                    }),
                    blockType: BlockType.COMMAND,
                    arguments: {
                        LED_ID: {
                            type: ArgumentType.NUMBER,
                            menu: 'LED_ID',
                            defaultValue: ApitorQ_LedID.ALL,
                        },
                        LED_COLOR_ID: {
                            type: ArgumentType.NUMBER,
                            menu: 'LED_COLOR_ID',
                            defaultValue: ApitorQ_LedColorID.RED,
                        },
                        ON_TIME: {
                            type: ArgumentType.NUMBER,
                            defaultValue: 1,
                        },
                        OFF_TIME: {
                            type: ArgumentType.NUMBER,
                            defaultValue: 1,
                        },
                    }
                },
                {
                    opcode: 'reporterInfrared1',
                    text: formatMessage({
                        id: 'apitor.reporterInfrared1',
                        default: 'infrared1 sensor',
                        description: 'Apitor Robot X: the value returned by infrared1 sensor',
                    }),
                    blockType: BlockType.REPORTER,
                },
                {
                    opcode: 'reporterColor',
                    text: formatMessage({
                        id: 'apitor.reporterColor',
                        default: 'color sensor',
                        description: 'Apitor Robot Q: the value returned by color sensor',
                    }),
                    blockType: BlockType.REPORTER,
                },
                {
                    opcode: 'hatInfrared',
                    text: formatMessage({
                        id: 'apitor.hatInfrared',
                        default: 'when infrared sensor [INFRARED_ID] [OP] [REFERENCE]',
                        description: 'Apitor Robot X: when infrared sensor is < or = or > than reference',
                    }),
                    blockType: BlockType.HAT,
                    arguments: {
                        INFRARED_ID: {
                            type: ArgumentType.STRING,
                            menu: 'INFRARED_ID',
                            defaultValue: ApitorQ_InfraredID.R1,
                        },
                        OP: {
                            type: ArgumentType.STRING,
                            menu: 'OP',
                            defaultValue: '<',
                        },
                        REFERENCE: {
                            type: ArgumentType.NUMBER,
                            defaultValue: 7,
                        },
                    },
                },
                {
                    opcode: 'hatColor',
                    text: formatMessage({
                        id: 'apitor.hatColor',
                        default: 'when color sensor sees [SENSOR_COLOR_ID]',
                        description: 'Apitor Robot Q: when color is equal to reference',
                    }),
                    blockType: BlockType.HAT,
                    arguments: {
                        SENSOR_COLOR_ID: {
                            type: ArgumentType.NUMBER,
                            menu: 'SENSOR_COLOR_ID',
                            defaultValue: ApitorQ_SensorColorID.R,
                        },
                    },
                },
                {
                    opcode: 'booleanInfrared',
                    text: formatMessage({
                        id: 'apitor.booleanInfrared',
                        default: 'when infrared sensor [INFRARED_ID] [OP] [REFERENCE]',
                        description: 'Apitor Robot X: when infrared sensor is < or = or > than reference',
                    }),
                    blockType: BlockType.BOOLEAN,
                    arguments: {
                        INFRARED_ID: {
                            type: ArgumentType.STRING,
                            menu: 'INFRARED_ID',
                            defaultValue: ApitorQ_InfraredID.R1,
                        },
                        OP: {
                            type: ArgumentType.STRING,
                            menu: 'OP',
                            defaultValue: '<',
                        },
                        REFERENCE: {
                            type: ArgumentType.NUMBER,
                            defaultValue: 7,
                        },
                    },
                },
                {
                    opcode: 'booleanColor',
                    text: formatMessage({
                        id: 'apitor.booleanColor',
                        default: 'when color sensor sees [SENSOR_COLOR_ID]',
                        description: 'Apitor Robot Q: when color is equal to reference',
                    }),
                    blockType: BlockType.BOOLEAN,
                    arguments: {
                        SENSOR_COLOR_ID: {
                            type: ArgumentType.NUMBER,
                            menu: 'SENSOR_COLOR_ID',
                            defaultValue: ApitorQ_SensorColorID.R,
                        },
                    },
                },
            ],
            menus: {
                MOTOR_ID: {
                    acceptReporters: false,
                    items: [
                        {
                            text: formatMessage({
                                id: 'apitor.motorId.m1',
                                default: 'M1',
                                description: 'motor M1',
                            }),
                            value: ApitorQ_MotorID.M1,
                        },
                        {
                            text: formatMessage({
                                id: 'apitor.motorId.m2',
                                default: 'M2',
                                description: 'motor M2',
                            }),
                            value: ApitorQ_MotorID.M2,
                        },
                        {
                            text: formatMessage({
                                id: 'apitor.motorId.all',
                                default: 'all',
                                description: 'all motors at once',
                            }),
                            value: ApitorQ_MotorID.ALL,
                        },
                    ],
                },
                MOTOR_DIRECTION_ID: {
                    acceptReporters: false,
                    items: [
                        {
                            text: formatMessage({
                                id: 'apitor.motorDirectionId.d1',
                                default: '↩',
                                description: 'clockwise direction',
                            }),
                            value: ApitorQ_MotorDirectionID.D1,
                        },
                        {
                            text: formatMessage({
                                id: 'apitor.motorDirectionId.d2',
                                default: '↪',
                                description: 'counter-clockwise direction',
                            }),
                            value: ApitorQ_MotorDirectionID.D2,
                        },
                    ],
                },
                MOTOR_SPEED: {
                    acceptReporters: false,
                    items: [
                        {
                            text: '1',
                            value: 1,
                        },
                        {
                            text: '2',
                            value: 2,
                        },
                        {
                            text: '3',
                            value: 3,
                        },
                        {
                            text: '4',
                            value: 4,
                        },
                        {
                            text: '5',
                            value: 5,
                        },
                        {
                            text: '6',
                            value: 6,
                        },
                        {
                            text: '7',
                            value: 7,
                        },
                        {
                            text: '8',
                            value: 8,
                        },
                        {
                            text: '9',
                            value: 9,
                        },
                        {
                            text: '10',
                            value: 10,
                        },
                        {
                            text: '11',
                            value: 11,
                        },
                        {
                            text: '12',
                            value: 12,
                        },
                        {
                            text: '13',
                            value: 13,
                        },
                        {
                            text: '14',
                            value: 14,
                        },
                        {
                            text: '15',
                            value: 15,
                        },
                        {
                            text: '16',
                            value: 16,
                        },
                    ],
                },
                INFRARED_ID: {
                    acceptReporters: false,
                    items: [
                        {
                            text: formatMessage({
                                id: 'apitor.infraredId.r1',
                                default: 'R1',
                                description: 'infrared sensor R1',
                            }),
                            value: ApitorQ_InfraredID.R1,
                        },
                    ],
                },
                LED_ID: {
                    acceptReporters: false,
                    items: [
                        {
                            text: formatMessage({
                                id: 'apitor.ledId.l1',
                                default: 'L1',
                                description: 'LED labeled L1',
                            }),
                            value: ApitorQ_LedID.L1,
                        },
                        {
                            text: formatMessage({
                                id: 'apitor.ledId.l2',
                                default: 'L2',
                                description: 'LED labeled L2',
                            }),
                            value: ApitorQ_LedID.L2,
                        },
                        {
                            text: formatMessage({
                                id: 'apitor.ledId.all',
                                default: 'all',
                                description: 'All LEDs at once',
                            }),
                            value: ApitorQ_LedID.ALL,
                        },
                    ],
                },
                LED_COLOR_ID: {
                    acceptReporters: false,
                    items: [
                        {
                            text: formatMessage({
                                id: 'apitor.ledColorId.off',
                                default: 'off',
                                description: 'turn off',
                            }),
                            value: ApitorQ_LedColorID.OFF,
                        },
                        {
                            text: formatMessage({
                                id: 'apitor.ledColorId.red',
                                default: 'red',
                                description: 'red color',
                            }),
                            value: ApitorQ_LedColorID.RED,
                        },
                        {
                            text: formatMessage({
                                id: 'apitor.ledColorId.orange',
                                default: 'orange',
                                description: 'orange color',
                            }),
                            value: ApitorQ_LedColorID.ORANGE,
                        },
                        {
                            text: formatMessage({
                                id: 'apitor.ledColorId.yellow',
                                default: 'yellow',
                                description: 'yellow color',
                            }),
                            value: ApitorQ_LedColorID.YELLOW,
                        },
                        {
                            text: formatMessage({
                                id: 'apitor.ledColorId.green',
                                default: 'green',
                                description: 'green color',
                            }),
                            value: ApitorQ_LedColorID.GREEN,
                        },
                        {
                            text: formatMessage({
                                id: 'apitor.ledColorId.cyan',
                                default: 'cyan',
                                description: 'cyan color',
                            }),
                            value: ApitorQ_LedColorID.CYAN,
                        },
                        {
                            text: formatMessage({
                                id: 'apitor.ledColorId.blue',
                                default: 'blue',
                                description: 'blue color',
                            }),
                            value: ApitorQ_LedColorID.BLUE,
                        },
                        {
                            text: formatMessage({
                                id: 'apitor.ledColorId.purple',
                                default: 'purple',
                                description: 'purple color',
                            }),
                            value: ApitorQ_LedColorID.PURPLE,
                        },
                    ],
                },
                OP: {
                    acceptReporters: false,
                    items: ['<', '=', '>'],
                },
                SENSOR_COLOR_ID: {
                    acceptReporters: false,
                    items: [
                        {
                            text: formatMessage({
                                id: 'apitor.colorId.r',
                                default: 'red',
                                description: 'red color',
                            }),
                            value: ApitorQ_SensorColorID.R,
                        },
                        {
                            text: formatMessage({
                                id: 'apitor.colorId.g',
                                default: 'green',
                                description: 'green color',
                            }),
                            value: ApitorQ_SensorColorID.G,
                        },
                        {
                            text: formatMessage({
                                id: 'apitor.colorId.b',
                                default: 'blue',
                                description: 'blue color',
                            }),
                            value: ApitorQ_SensorColorID.B,
                        },
                        {
                            text: formatMessage({
                                id: 'apitor.colorId.x',
                                default: 'other',
                                description: 'other color',
                            }),
                            value: ApitorQ_SensorColorID.X,
                        },
                    ],
                },
            },
        };
    }

    /**
     * Turn specified motor(s) on indefinitely.
     * @param    {object}                   args               - the block's arguments.
     * @property {ApitorQ_MotorID}          MOTOR_ID           - the motor(s) to be affected.
     * @property {ApitorQ_MotorDirectionID} MOTOR_DIRECTION_ID - the new power level for the motor(s).
     * @property {number}                   MOTOR_SPEED        - the new power level for the motor(s).
     * @return {Promise} - a Promise that resolves after some delay.
     */
    commandMotorOn (args) {
        let id = Cast.toNumber(args.MOTOR_ID);
        let speed = Cast.toNumber(args.MOTOR_SPEED);
        let dir = Cast.toNumber(args.MOTOR_DIRECTION_ID);

        if (dir == ApitorQ_MotorDirectionID.D2) {
            speed = -speed;
        }

        this._peripheral.setMotor(id, speed);

        return new Promise(resolve => {
            window.setTimeout(() => {
                resolve();
            }, BLESendInterval);
        });
    }

    /**
     * Turn specified motor(s) off.
     * @param    {object}          args     - the block's arguments.
     * @property {ApitorQ_MotorID} MOTOR_ID - the motor(s) to deactivate.
     * @return   {Promise} - a Promise that resolves after some delay.
     */
    commandMotorOff (args) {
        let id = Cast.toNumber(args.MOTOR_ID);
        this._peripheral.setMotor(id, 0);

        return new Promise(resolve => {
            window.setTimeout(() => {
                resolve();
            }, BLESendInterval);
        });
    }

    /**
     * Set the LED's color.
     * @param    {object}             args         - the block's arguments.
     * @property {ApitorQ_LedID}      LED_ID       - see setLED()
     * @property {ApitorQ_LedColorID} LED_COLOR_ID - see setLED()
     * @return {Promise} - a Promise that resolves after some delay.
     */
    commandSetLedOn (args) {
        let id = Cast.toNumber(args.LED_ID);
        let color = Cast.toNumber(args.LED_COLOR_ID);
        color = MathUtil.wrapClamp(color, 0, 7);
        this._peripheral.setLED(id, color, 0, 0);

        return new Promise(resolve => {
            window.setTimeout(() => {
                resolve();
            }, BLESendInterval);
        });
    }

    /**
     * Set the LED's color.
     * @param    {object}             args         - the block's arguments.
     * @property {ApitorQ_LedID}      LED_ID       - see setLED()
     * @property {ApitorQ_LedColorID} LED_COLOR_ID - see setLED()
     * @property {number}             ON_TIME      - see setLED()
     * @property {number}             OFF_TIME     - see setLED()
     * @return {Promise} - a Promise that resolves after some delay.
     */
    commandSetLedBlink (args) {
        let id = Cast.toNumber(args.LED_ID);
        let color = Cast.toNumber(args.LED_COLOR_ID);
        color = MathUtil.wrapClamp(color, 0, 7);
        let ontime = Cast.toNumber(args.ON_TIME);
        let offtime = Cast.toNumber(args.OFF_TIME);
        this._peripheral.setLED(id, color, ontime, offtime);

        return new Promise(resolve => {
            window.setTimeout(() => {
                resolve();
            }, BLESendInterval);
        });
    }

    /**
     * @return {number} - the infrared1 sensor's value.
     */
    reporterInfrared1 () {
        return this._peripheral.sensorInfrared1;
    }

    /**
     * @return {number} - the color sensor's value.
     */
    reporterColor () {
        return this._peripheral.sensorColor;
    }

    /**
     * Compare the infrared sensor's value to a reference.
     * @param    {object} args                    - the block's arguments.
     * @property {ApitorQ_InfraredID} INFRARED_ID - infrared sensor ID
     * @property {string} OP                      - the comparison operation, one of '<=>'.
     * @property {number} REFERENCE               - the value to compare against.
     * @return {boolean} - the result of the comparison, or false on error.
     */
    hatInfrared (args) {
        let id = Cast.toNumber(args.INFRARED_ID);
        let reference = Cast.toNumber(args.REFERENCE);

        let value = this._peripheral.sensorInfrared1;

        switch (args.OP) {
        case '<':
            return value < reference;
        case '=':
            return value == reference;
        case '>':
            return value > reference;
        default:
            log.warn(`Unknown comparison operator in hatInfrared: ${args.OP}`);
            return false;
        }
    }

    /**
     * Compare the color sensor's value to a reference.
     * @param    {object}                args            - the block's arguments.
     * @property {ApitorQ_SensorColorID} SENSOR_COLOR_ID - the value to compare against.
     * @return {boolean} - the result of the comparison, or false on error.
     */
    hatColor (args) {
        return this._peripheral.sensorColor == Cast.toNumber(args.SENSOR_COLOR_ID);
    }

    /**
     * Similar to hatInfrared()
     */
    booleanInfrared (args) {
        return this.hatInfrared(args);
    }

    /**
     * Similar to hatColor()
     */
    booleanColor (args) {
        return this.hatColor(args);
    }
}

module.exports = Scratch3ApitorQBlocks;
