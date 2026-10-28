import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7680 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7680 = true := by
  decide +kernel

theorem tot7680 : totK PD2M8K2 D2M8K2.t7680 = [0, 0, 185998154775, 466618506347, 243605211077, 16666837446, 0, 0] := by
  decide +kernel

theorem rows7681 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7681 = true := by
  decide +kernel

theorem tot7681 : totK PD2M8K2 D2M8K2.t7681 = [0, 0, 158608021086, 462314565568, 273199875760, 25114097147, 0, 0] := by
  decide +kernel

theorem rows7682 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7682 = true := by
  decide +kernel

theorem tot7682 : totK PD2M8K2 D2M8K2.t7682 = [0, 0, 0, 201169453830, 464752814517, 228985639440, 19027531247, 0] := by
  decide +kernel

theorem rows7683 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7683 = true := by
  decide +kernel

theorem tot7683 : totK PD2M8K2 D2M8K2.t7683 = [0, 0, 28526375756, 235563824213, 474819718821, 161078903518, 5656105375, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
