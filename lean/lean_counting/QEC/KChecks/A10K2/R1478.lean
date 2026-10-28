import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5912 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5912 = true := by
  decide +kernel

theorem tot5912 : totK PA10K2 A10K2.t5912 = [0, 292923624175, 1270835356412, 1926030149426, 1110672274116, 185169835903, 5410721913, 0, 0, 0] := by
  decide +kernel

theorem rows5913 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5913 = true := by
  decide +kernel

theorem tot5913 : totK PA10K2 A10K2.t5913 = [0, 386897682605, 1594415768750, 1843083279250, 570466712343, 38164436003, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5914 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5914 = true := by
  decide +kernel

theorem tot5914 : totK PA10K2 A10K2.t5914 = [0, 185564004214, 1020539671227, 1914287071364, 1167349538064, 172237192518, 5546304973, 0, 0, 0] := by
  decide +kernel

theorem rows5915 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5915 = true := by
  decide +kernel

theorem tot5915 : totK PA10K2 A10K2.t5915 = [0, 598986562898, 2040216734064, 2014794447230, 478943029696, 27011302452, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
