import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5808 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5808 = true := by
  decide +kernel

theorem tot5808 : totK PA10K2 A10K2.t5808 = [0, 0, 95577804451, 1190535079556, 2279576600363, 1042686970581, 86383984202, 0, 0, 0] := by
  decide +kernel

theorem rows5809 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5809 = true := by
  decide +kernel

theorem tot5809 : totK PA10K2 A10K2.t5809 = [0, 0, 368063465345, 1356202425720, 1851196772937, 1077461953642, 209038318113, 6354482628, 0, 0] := by
  decide +kernel

theorem rows5810 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5810 = true := by
  decide +kernel

theorem tot5810 : totK PA10K2 A10K2.t5810 = [0, 0, 260403760671, 1432701938461, 2251324139441, 1051757388714, 81140713601, 0, 0, 0] := by
  decide +kernel

theorem rows5811 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5811 = true := by
  decide +kernel

theorem tot5811 : totK PA10K2 A10K2.t5811 = [0, 0, 0, 573282833259, 2097594988654, 1957855082361, 399664951872, 12926121504, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
