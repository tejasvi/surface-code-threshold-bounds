import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13536 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13536 = true := by
  decide +kernel

theorem tot13536 : totK PD2M8K2 D2M8K2.t13536 = [179595312347, 456748385007, 219448943003, 47022415186, 8621106361, 0, 0, 0] := by
  decide +kernel

theorem rows13537 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13537 = true := by
  decide +kernel

theorem tot13537 : totK PD2M8K2 D2M8K2.t13537 = [203705243845, 454466751932, 202904522537, 12530154330, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13538 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13538 = true := by
  decide +kernel

theorem tot13538 : totK PD2M8K2 D2M8K2.t13538 = [35823478819, 316191099868, 442639191350, 98784932688, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows13539 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13539 = true := by
  decide +kernel

theorem tot13539 : totK PD2M8K2 D2M8K2.t13539 = [70546937106, 354732840186, 426430949552, 54757664695, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
