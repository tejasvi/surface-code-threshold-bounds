import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5928 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5928 = true := by
  decide +kernel

theorem tot5928 : totK PD2M8K2 D2M8K2.t5928 = [64775187903, 293215510584, 392258906785, 134171946841, 9511901980, 0, 0, 0] := by
  decide +kernel

theorem rows5929 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5929 = true := by
  decide +kernel

theorem tot5929 : totK PD2M8K2 D2M8K2.t5929 = [178019329563, 453373392061, 261361093748, 26449386691, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5930 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5930 = true := by
  decide +kernel

theorem tot5930 : totK PD2M8K2 D2M8K2.t5930 = [142778969255, 449329416039, 292646696587, 22732087164, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5931 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5931 = true := by
  decide +kernel

theorem tot5931 : totK PD2M8K2 D2M8K2.t5931 = [0, 213670544129, 479329248931, 183151124000, 9565108570, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
