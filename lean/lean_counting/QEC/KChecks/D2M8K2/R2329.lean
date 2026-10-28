import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9316 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9316 = true := by
  decide +kernel

theorem tot9316 : totK PD2M8K2 D2M8K2.t9316 = [0, 155776178420, 464971966873, 242474367801, 13494115512, 0, 0, 0] := by
  decide +kernel

theorem rows9317 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9317 = true := by
  decide +kernel

theorem tot9317 : totK PD2M8K2 D2M8K2.t9317 = [0, 185710200723, 464337651140, 230616827177, 13698234747, 0, 0, 0] := by
  decide +kernel

theorem rows9318 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9318 = true := by
  decide +kernel

theorem tot9318 : totK PD2M8K2 D2M8K2.t9318 = [0, 189941488154, 480144845391, 221980517031, 12443528988, 0, 0, 0] := by
  decide +kernel

theorem rows9319 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9319 = true := by
  decide +kernel

theorem tot9319 : totK PD2M8K2 D2M8K2.t9319 = [0, 215455607703, 493524702852, 185442973637, 5086124964, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
