import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13756 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13756 = true := by
  decide +kernel

theorem tot13756 : totK PD2M8K2 D2M8K2.t13756 = [0, 161253977111, 380754682081, 264742502183, 82571960729, 3884009855, 0, 0] := by
  decide +kernel

theorem rows13757 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13757 = true := by
  decide +kernel

theorem tot13757 : totK PD2M8K2 D2M8K2.t13757 = [0, 165692823816, 453047269749, 241126942236, 16954357240, 0, 0, 0] := by
  decide +kernel

theorem rows13758 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13758 = true := by
  decide +kernel

theorem tot13758 : totK PD2M8K2 D2M8K2.t13758 = [0, 89411507079, 369919040297, 365265396725, 70700004181, 1369150432, 0, 0] := by
  decide +kernel

theorem rows13759 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13759 = true := by
  decide +kernel

theorem tot13759 : totK PD2M8K2 D2M8K2.t13759 = [0, 0, 306569554099, 513631706397, 76472114823, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
