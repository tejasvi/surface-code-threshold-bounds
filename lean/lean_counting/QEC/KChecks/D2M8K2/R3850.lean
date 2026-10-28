import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15400 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15400 = true := by
  decide +kernel

theorem tot15400 : totK PD2M8K2 D2M8K2.t15400 = [0, 0, 194920179277, 478499944118, 214941463462, 10862667398, 0, 0] := by
  decide +kernel

theorem rows15401 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15401 = true := by
  decide +kernel

theorem tot15401 : totK PD2M8K2 D2M8K2.t15401 = [0, 0, 0, 381187865279, 457328578649, 42894359375, 0, 0] := by
  decide +kernel

theorem rows15402 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15402 = true := by
  decide +kernel

theorem tot15402 : totK PD2M8K2 D2M8K2.t15402 = [0, 0, 167359180155, 409025011290, 259442478428, 51271515797, 1330264907, 0] := by
  decide +kernel

theorem rows15403 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15403 = true := by
  decide +kernel

theorem tot15403 : totK PD2M8K2 D2M8K2.t15403 = [0, 0, 158082287158, 443073483817, 281011899847, 26612677673, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
