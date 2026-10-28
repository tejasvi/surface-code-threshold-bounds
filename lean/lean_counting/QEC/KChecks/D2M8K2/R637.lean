import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2548 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2548 = true := by
  decide +kernel

theorem tot2548 : totK PD2M8K2 D2M8K2.t2548 = [0, 180937872387, 472527221832, 245671310453, 13457381083, 0, 0, 0] := by
  decide +kernel

theorem rows2549 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2549 = true := by
  decide +kernel

theorem tot2549 : totK PD2M8K2 D2M8K2.t2549 = [156139380478, 389226111958, 233460106830, 91681096923, 12292191758, 0, 0, 0] := by
  decide +kernel

theorem rows2550 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2550 = true := by
  decide +kernel

theorem tot2550 : totK PD2M8K2 D2M8K2.t2550 = [163001771088, 464026623493, 253568225130, 15151135220, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2551 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2551 = true := by
  decide +kernel

theorem tot2551 : totK PD2M8K2 D2M8K2.t2551 = [0, 282877376294, 498275093436, 104467472099, 1369150432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
