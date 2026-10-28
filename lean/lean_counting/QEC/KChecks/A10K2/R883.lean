import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3532 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3532 = true := by
  decide +kernel

theorem tot3532 : totK PA10K2 A10K2.t3532 = [0, 0, 291926293321, 1249095766183, 1894408661790, 1195033468592, 199600107840, 6034215561, 0, 0] := by
  decide +kernel

theorem rows3533 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3533 = true := by
  decide +kernel

theorem tot3533 : totK PA10K2 A10K2.t3533 = [0, 0, 262925581067, 1449971526016, 2138825133312, 828375537941, 60211199503, 0, 0, 0] := by
  decide +kernel

theorem rows3534 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3534 = true := by
  decide +kernel

theorem tot3534 : totK PA10K2 A10K2.t3534 = [0, 0, 340596673582, 1301580052229, 1946980531691, 1069807040717, 170970216739, 5982052406, 0, 0] := by
  decide +kernel

theorem rows3535 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3535 = true := by
  decide +kernel

theorem tot3535 : totK PA10K2 A10K2.t3535 = [0, 0, 474535965045, 1821016847036, 2056378191691, 666364363528, 39629782531, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
