import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3084 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3084 = true := by
  decide +kernel

theorem tot3084 : totK PA10K2 A10K2.t3084 = [0, 0, 556621861187, 1664061226228, 1666574228152, 820357352889, 164382875557, 6354482628, 0, 0] := by
  decide +kernel

theorem rows3085 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3085 = true := by
  decide +kernel

theorem tot3085 : totK PA10K2 A10K2.t3085 = [0, 0, 0, 816419554707, 2302325410078, 1591921095737, 234082498394, 6725424603, 0, 0] := by
  decide +kernel

theorem rows3086 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3086 = true := by
  decide +kernel

theorem tot3086 : totK PA10K2 A10K2.t3086 = [0, 0, 496142183130, 1764604243900, 1930652605391, 706933651589, 65192132021, 0, 0, 0] := by
  decide +kernel

theorem rows3087 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3087 = true := by
  decide +kernel

theorem tot3087 : totK PA10K2 A10K2.t3087 = [0, 0, 304353275390, 1469024504829, 2157784825685, 945462564756, 83084434878, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
