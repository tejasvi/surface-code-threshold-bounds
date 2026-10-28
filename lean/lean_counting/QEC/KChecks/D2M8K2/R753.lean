import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3012 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3012 = true := by
  decide +kernel

theorem tot3012 : totK PD2M8K2 D2M8K2.t3012 = [0, 81258097990, 233960314141, 378717301852, 183632446046, 12866082196, 0, 0] := by
  decide +kernel

theorem rows3013 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3013 = true := by
  decide +kernel

theorem tot3013 : totK PD2M8K2 D2M8K2.t3013 = [0, 150494843437, 466614099531, 250188843754, 13524536781, 0, 0, 0] := by
  decide +kernel

theorem rows3014 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3014 = true := by
  decide +kernel

theorem tot3014 : totK PD2M8K2 D2M8K2.t3014 = [0, 161010211928, 448792441953, 251960122716, 16845411046, 0, 0, 0] := by
  decide +kernel

theorem rows3015 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3015 = true := by
  decide +kernel

theorem tot3015 : totK PD2M8K2 D2M8K2.t3015 = [0, 0, 268881964751, 497103792472, 99646085570, 1334361349, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
