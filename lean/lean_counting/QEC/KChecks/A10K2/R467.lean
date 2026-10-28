import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1868 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1868 = true := by
  decide +kernel

theorem tot1868 : totK PA10K2 A10K2.t1868 = [0, 0, 586827950721, 1888140384194, 1782522219054, 481373820518, 31614405859, 0, 0, 0] := by
  decide +kernel

theorem rows1869 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1869 = true := by
  decide +kernel

theorem tot1869 : totK PA10K2 A10K2.t1869 = [0, 0, 14257594719, 1058584695202, 2371647577331, 1116479853882, 92431429569, 0, 0, 0] := by
  decide +kernel

theorem rows1870 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1870 = true := by
  decide +kernel

theorem tot1870 : totK PA10K2 A10K2.t1870 = [0, 0, 485216937829, 1672863930908, 1850507577178, 773001589187, 133798624358, 5705019915, 0, 0] := by
  decide +kernel

theorem rows1871 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1871 = true := by
  decide +kernel

theorem tot1871 : totK PA10K2 A10K2.t1871 = [0, 0, 314008318368, 1487864756759, 2152304105213, 944815758113, 83540878628, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
