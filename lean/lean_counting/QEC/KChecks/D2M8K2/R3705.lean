import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14820 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14820 = true := by
  decide +kernel

theorem tot14820 : totK PD2M8K2 D2M8K2.t14820 = [0, 285311959404, 499286398331, 110606476849, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows14821 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14821 = true := by
  decide +kernel

theorem tot14821 : totK PD2M8K2 D2M8K2.t14821 = [0, 209096768897, 482802671469, 189940968467, 7439461435, 0, 0, 0] := by
  decide +kernel

theorem rows14822 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14822 = true := by
  decide +kernel

theorem tot14822 : totK PD2M8K2 D2M8K2.t14822 = [0, 189764724770, 474460511004, 216072139095, 14704558535, 0, 0, 0] := by
  decide +kernel

theorem rows14823 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14823 = true := by
  decide +kernel

theorem tot14823 : totK PD2M8K2 D2M8K2.t14823 = [0, 148988721421, 450974613360, 240163301954, 13450165506, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
