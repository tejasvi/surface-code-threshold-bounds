import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows68 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t68 = true := by
  decide +kernel

theorem tot68 : totK PD2M8K2 D2M8K2.t68 = [104904165133, 326338504848, 320657979714, 143270595761, 13566920432, 0, 0, 0] := by
  decide +kernel

theorem rows69 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t69 = true := by
  decide +kernel

theorem tot69 : totK PD2M8K2 D2M8K2.t69 = [190018822883, 463225371249, 228143235117, 17111997474, 0, 0, 0, 0] := by
  decide +kernel

theorem rows70 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t70 = true := by
  decide +kernel

theorem tot70 : totK PD2M8K2 D2M8K2.t70 = [123641764684, 433942808088, 308348442148, 28492415024, 0, 0, 0, 0] := by
  decide +kernel

theorem rows71 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t71 = true := by
  decide +kernel

theorem tot71 : totK PD2M8K2 D2M8K2.t71 = [0, 275429993472, 511130671816, 110355431096, 1369150432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
