import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2796 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2796 = true := by
  decide +kernel

theorem tot2796 : totK PD2M8K2 D2M8K2.t2796 = [86391183362, 350604198273, 374637810877, 80125543510, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows2797 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2797 = true := by
  decide +kernel

theorem tot2797 : totK PD2M8K2 D2M8K2.t2797 = [0, 327246845604, 510515091524, 67067336476, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2798 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2798 = true := by
  decide +kernel

theorem tot2798 : totK PD2M8K2 D2M8K2.t2798 = [196367285455, 453073120588, 239445361825, 27487495649, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2799 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2799 = true := by
  decide +kernel

theorem tot2799 : totK PD2M8K2 D2M8K2.t2799 = [187924304157, 465467660147, 225039235524, 12373752831, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
