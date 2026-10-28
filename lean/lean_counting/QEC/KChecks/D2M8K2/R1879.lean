import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7516 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7516 = true := by
  decide +kernel

theorem tot7516 : totK PD2M8K2 D2M8K2.t7516 = [0, 183911275284, 445877266645, 274775531055, 32504000310, 0, 0, 0] := by
  decide +kernel

theorem rows7517 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7517 = true := by
  decide +kernel

theorem tot7517 : totK PD2M8K2 D2M8K2.t7517 = [0, 144885510996, 454311224109, 284676026100, 28940256954, 0, 0, 0] := by
  decide +kernel

theorem rows7518 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7518 = true := by
  decide +kernel

theorem tot7518 : totK PD2M8K2 D2M8K2.t7518 = [0, 0, 222766792722, 492569279973, 165454079238, 7024963918, 0, 0] := by
  decide +kernel

theorem rows7519 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7519 = true := by
  decide +kernel

theorem tot7519 : totK PD2M8K2 D2M8K2.t7519 = [0, 156219903603, 435730353823, 285192659419, 36685398627, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
