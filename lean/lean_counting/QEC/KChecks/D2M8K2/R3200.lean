import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12800 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12800 = true := by
  decide +kernel

theorem tot12800 : totK PD2M8K2 D2M8K2.t12800 = [0, 0, 202349165587, 494507814474, 190616654013, 9668735432, 0, 0] := by
  decide +kernel

theorem rows12801 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12801 = true := by
  decide +kernel

theorem tot12801 : totK PD2M8K2 D2M8K2.t12801 = [0, 77658537643, 315478664443, 379911327103, 102164022646, 3581949829, 0, 0] := by
  decide +kernel

theorem rows12802 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12802 = true := by
  decide +kernel

theorem tot12802 : totK PD2M8K2 D2M8K2.t12802 = [0, 162772019938, 436960511559, 278802667363, 30330618207, 0, 0, 0] := by
  decide +kernel

theorem rows12803 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12803 = true := by
  decide +kernel

theorem tot12803 : totK PD2M8K2 D2M8K2.t12803 = [0, 173357483096, 475625481406, 249502254095, 13916467904, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
