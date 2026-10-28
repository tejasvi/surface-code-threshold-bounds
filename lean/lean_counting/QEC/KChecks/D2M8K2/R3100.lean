import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12400 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12400 = true := by
  decide +kernel

theorem tot12400 : totK PD2M8K2 D2M8K2.t12400 = [0, 98090759061, 415345880122, 352216404715, 42812147577, 0, 0, 0] := by
  decide +kernel

theorem rows12401 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12401 = true := by
  decide +kernel

theorem tot12401 : totK PD2M8K2 D2M8K2.t12401 = [0, 0, 208773878921, 475907517022, 218874830378, 13604428459, 0, 0] := by
  decide +kernel

theorem rows12402 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12402 = true := by
  decide +kernel

theorem tot12402 : totK PD2M8K2 D2M8K2.t12402 = [0, 97657982275, 337731985096, 362473747658, 95766618456, 1409560813, 0, 0] := by
  decide +kernel

theorem rows12403 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12403 = true := by
  decide +kernel

theorem tot12403 : totK PD2M8K2 D2M8K2.t12403 = [0, 170340926752, 445700399548, 277094664393, 29782994895, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
