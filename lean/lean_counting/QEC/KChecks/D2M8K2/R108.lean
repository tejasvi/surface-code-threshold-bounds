import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows432 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t432 = true := by
  decide +kernel

theorem tot432 : totK PD2M8K2 D2M8K2.t432 = [0, 199851092768, 486935914604, 193882564877, 9650260530, 0, 0, 0] := by
  decide +kernel

theorem rows433 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t433 = true := by
  decide +kernel

theorem tot433 : totK PD2M8K2 D2M8K2.t433 = [174300440406, 457110291122, 259355188659, 29438067803, 0, 0, 0, 0] := by
  decide +kernel

theorem rows434 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t434 = true := by
  decide +kernel

theorem tot434 : totK PD2M8K2 D2M8K2.t434 = [172201522489, 448196038984, 264875814354, 22070881804, 0, 0, 0, 0] := by
  decide +kernel

theorem rows435 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t435 = true := by
  decide +kernel

theorem tot435 : totK PD2M8K2 D2M8K2.t435 = [93763323609, 352152376518, 376443776278, 78437389851, 1268739303, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
