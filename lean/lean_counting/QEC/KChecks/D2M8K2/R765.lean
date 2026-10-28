import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3060 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3060 = true := by
  decide +kernel

theorem tot3060 : totK PD2M8K2 D2M8K2.t3060 = [0, 187090589606, 460979880278, 253021545410, 19835692192, 0, 0, 0] := by
  decide +kernel

theorem rows3061 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3061 = true := by
  decide +kernel

theorem tot3061 : totK PD2M8K2 D2M8K2.t3061 = [0, 139955743058, 448075665988, 286082916634, 20017574353, 0, 0, 0] := by
  decide +kernel

theorem rows3062 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3062 = true := by
  decide +kernel

theorem tot3062 : totK PD2M8K2 D2M8K2.t3062 = [0, 0, 261689308026, 509414710164, 118216505543, 2116456933, 0, 0] := by
  decide +kernel

theorem rows3063 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3063 = true := by
  decide +kernel

theorem tot3063 : totK PD2M8K2 D2M8K2.t3063 = [0, 172268089426, 415625273537, 247332379148, 53559601832, 2569691499, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
