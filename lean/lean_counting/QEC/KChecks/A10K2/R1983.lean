import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7932 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7932 = true := by
  decide +kernel

theorem tot7932 : totK PA10K2 A10K2.t7932 = [0, 325349547516, 1411742855254, 2044323837301, 1069460968252, 156763816808, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7933 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7933 = true := by
  decide +kernel

theorem tot7933 : totK PA10K2 A10K2.t7933 = [0, 571085190322, 1963754777421, 1935343418235, 533919591795, 30742319898, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7934 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7934 = true := by
  decide +kernel

theorem tot7934 : totK PA10K2 A10K2.t7934 = [0, 0, 744558030056, 2181379002158, 1713697387645, 308328394756, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows7935 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7935 = true := by
  decide +kernel

theorem tot7935 : totK PA10K2 A10K2.t7935 = [0, 0, 402901744251, 1723990027927, 2175900319239, 752327351123, 56143165367, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
