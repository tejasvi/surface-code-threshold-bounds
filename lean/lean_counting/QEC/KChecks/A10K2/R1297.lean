import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5188 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5188 = true := by
  decide +kernel

theorem tot5188 : totK PA10K2 A10K2.t5188 = [0, 0, 112706332773, 727094360512, 1803046859805, 1557965335156, 374397805729, 15704651987, 0, 0] := by
  decide +kernel

theorem rows5189 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5189 = true := by
  decide +kernel

theorem tot5189 : totK PA10K2 A10K2.t5189 = [0, 0, 504283203485, 1813592443417, 1865275480550, 518924345574, 31608797364, 0, 0, 0] := by
  decide +kernel

theorem rows5190 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5190 = true := by
  decide +kernel

theorem tot5190 : totK PA10K2 A10K2.t5190 = [0, 0, 107927970516, 1237977550084, 2272659459329, 912411678438, 65326404304, 0, 0, 0] := by
  decide +kernel

theorem rows5191 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5191 = true := by
  decide +kernel

theorem tot5191 : totK PA10K2 A10K2.t5191 = [0, 0, 438287101615, 1501653711325, 1803304049944, 903189793969, 153851967938, 5546304973, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
