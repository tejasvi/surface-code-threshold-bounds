import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows200 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t200 = true := by
  decide +kernel

theorem tot200 : totK PA10K2 A10K2.t200 = [0, 0, 633720649845, 2096336558472, 1953337820034, 440548031033, 13242594235, 0, 0, 0] := by
  decide +kernel

theorem rows201 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t201 = true := by
  decide +kernel

theorem tot201 : totK PA10K2 A10K2.t201 = [0, 0, 297605501296, 1548233746284, 2206807201425, 859329962952, 75177836158, 0, 0, 0] := by
  decide +kernel

theorem rows202 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t202 = true := by
  decide +kernel

theorem tot202 : totK PA10K2 A10K2.t202 = [0, 0, 293936207583, 1373159778107, 2154934596071, 1093341237901, 112063678536, 0, 0, 0] := by
  decide +kernel

theorem rows203 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t203 = true := by
  decide +kernel

theorem tot203 : totK PA10K2 A10K2.t203 = [0, 0, 458197478465, 1610547670755, 1892608128515, 921505222567, 186931191189, 7151180950, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
