import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13524 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13524 = true := by
  decide +kernel

theorem tot13524 : totK PD2M8K2 D2M8K2.t13524 = [0, 183622600134, 457099864348, 220170276097, 16632994142, 0, 0, 0] := by
  decide +kernel

theorem rows13525 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13525 = true := by
  decide +kernel

theorem tot13525 : totK PD2M8K2 D2M8K2.t13525 = [0, 95836991221, 417783099326, 325458544351, 33638808570, 0, 0, 0] := by
  decide +kernel

theorem rows13526 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13526 = true := by
  decide +kernel

theorem tot13526 : totK PD2M8K2 D2M8K2.t13526 = [0, 0, 302654092647, 454714464055, 100416726895, 1369150432, 0, 0] := by
  decide +kernel

theorem rows13527 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13527 = true := by
  decide +kernel

theorem tot13527 : totK PD2M8K2 D2M8K2.t13527 = [0, 175798146017, 460571217860, 236262746027, 17891173179, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
