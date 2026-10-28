import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14592 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14592 = true := by
  decide +kernel

theorem tot14592 : totK PD2M8K2 D2M8K2.t14592 = [0, 30623113973, 331829717169, 451114038795, 76360787459, 1107157161, 0, 0] := by
  decide +kernel

theorem rows14593 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14593 = true := by
  decide +kernel

theorem tot14593 : totK PD2M8K2 D2M8K2.t14593 = [0, 64502718389, 306634368152, 391487507980, 105489900247, 3824247485, 0, 0] := by
  decide +kernel

theorem rows14594 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14594 = true := by
  decide +kernel

theorem tot14594 : totK PD2M8K2 D2M8K2.t14594 = [0, 185142918105, 467541592062, 246243131533, 20104377587, 0, 0, 0] := by
  decide +kernel

theorem rows14595 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14595 = true := by
  decide +kernel

theorem tot14595 : totK PD2M8K2 D2M8K2.t14595 = [0, 189162093710, 480221412323, 230346718983, 12524207686, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
