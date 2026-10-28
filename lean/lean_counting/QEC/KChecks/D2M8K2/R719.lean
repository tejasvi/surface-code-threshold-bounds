import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2876 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2876 = true := by
  decide +kernel

theorem tot2876 : totK PD2M8K2 D2M8K2.t2876 = [0, 329991729388, 514513766130, 75520801056, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2877 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2877 = true := by
  decide +kernel

theorem tot2877 : totK PD2M8K2 D2M8K2.t2877 = [171716076782, 391098435235, 240973072548, 82205507450, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows2878 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2878 = true := by
  decide +kernel

theorem tot2878 : totK PD2M8K2 D2M8K2.t2878 = [156472272008, 441955645450, 281603744823, 24047074046, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2879 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2879 = true := by
  decide +kernel

theorem tot2879 : totK PD2M8K2 D2M8K2.t2879 = [92616578666, 347093840062, 367278100573, 81028959983, 1268739303, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
