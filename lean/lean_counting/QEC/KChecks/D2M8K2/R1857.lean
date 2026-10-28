import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7428 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7428 = true := by
  decide +kernel

theorem tot7428 : totK PD2M8K2 D2M8K2.t7428 = [0, 0, 212598032930, 488559641849, 188944541540, 7633840163, 0, 0] := by
  decide +kernel

theorem rows7429 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7429 = true := by
  decide +kernel

theorem tot7429 : totK PD2M8K2 D2M8K2.t7429 = [0, 0, 174251048033, 440641919260, 266124956707, 29185766107, 0, 0] := by
  decide +kernel

theorem rows7430 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7430 = true := by
  decide +kernel

theorem tot7430 : totK PD2M8K2 D2M8K2.t7430 = [0, 0, 178489649040, 496638590980, 219323255550, 9718425217, 0, 0] := by
  decide +kernel

theorem rows7431 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7431 = true := by
  decide +kernel

theorem tot7431 : totK PD2M8K2 D2M8K2.t7431 = [0, 0, 166155342896, 452505991182, 255254190830, 18039371491, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
