import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows24 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t24 = true := by
  decide +kernel

theorem tot24 : totK PD2M8K2 D2M8K2.t24 = [0, 155433023515, 453909002030, 268229384304, 18035581610, 0, 0, 0] := by
  decide +kernel

theorem rows25 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t25 = true := by
  decide +kernel

theorem tot25 : totK PD2M8K2 D2M8K2.t25 = [0, 180690053068, 467178482061, 221387393040, 12243442891, 0, 0, 0] := by
  decide +kernel

theorem rows26 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t26 = true := by
  decide +kernel

theorem tot26 : totK PD2M8K2 D2M8K2.t26 = [0, 200418641761, 481952485424, 210589663107, 10177609099, 0, 0, 0] := by
  decide +kernel

theorem rows27 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t27 = true := by
  decide +kernel

theorem tot27 : totK PD2M8K2 D2M8K2.t27 = [0, 192930132483, 466480577314, 221288148514, 12679943201, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
