import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13116 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13116 = true := by
  decide +kernel

theorem tot13116 : totK PD2M8K2 D2M8K2.t13116 = [0, 0, 153301681796, 457766018871, 286722280121, 27084257848, 0, 0] := by
  decide +kernel

theorem rows13117 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13117 = true := by
  decide +kernel

theorem tot13117 : totK PD2M8K2 D2M8K2.t13117 = [0, 90526249043, 261507761254, 333068609725, 198520623487, 17675683602, 0, 0] := by
  decide +kernel

theorem rows13118 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13118 = true := by
  decide +kernel

theorem tot13118 : totK PD2M8K2 D2M8K2.t13118 = [0, 171042326367, 454277870373, 239286484508, 17088974063, 0, 0, 0] := by
  decide +kernel

theorem rows13119 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13119 = true := by
  decide +kernel

theorem tot13119 : totK PD2M8K2 D2M8K2.t13119 = [0, 151696028697, 448191065270, 265927595726, 17052975866, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
