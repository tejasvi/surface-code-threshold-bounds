import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15680 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15680 = true := by
  decide +kernel

theorem tot15680 : totK PD2M8K2 D2M8K2.t15680 = [0, 0, 87191050473, 347834428259, 384621590032, 79085882041, 1164319620, 0] := by
  decide +kernel

theorem rows15681 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15681 = true := by
  decide +kernel

theorem tot15681 : totK PD2M8K2 D2M8K2.t15681 = [0, 0, 0, 258179075341, 501199763229, 122337505285, 4234510686, 0] := by
  decide +kernel

theorem rows15682 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15682 = true := by
  decide +kernel

theorem tot15682 : totK PD2M8K2 D2M8K2.t15682 = [0, 0, 180631317618, 472875863916, 237555971842, 13621868413, 0, 0] := by
  decide +kernel

theorem rows15683 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15683 = true := by
  decide +kernel

theorem tot15683 : totK PD2M8K2 D2M8K2.t15683 = [0, 0, 143671843041, 454441934983, 277783790919, 16864632375, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
