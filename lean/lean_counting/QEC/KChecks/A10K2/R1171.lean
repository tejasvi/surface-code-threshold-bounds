import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4684 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4684 = true := by
  decide +kernel

theorem tot4684 : totK PA10K2 A10K2.t4684 = [0, 297267720674, 1526134355741, 2147301071719, 883386693184, 77681195692, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4685 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4685 = true := by
  decide +kernel

theorem tot4685 : totK PA10K2 A10K2.t4685 = [0, 0, 535922014837, 1927844858027, 1874240500321, 498652450256, 31747192500, 0, 0, 0] := by
  decide +kernel

theorem rows4686 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4686 = true := by
  decide +kernel

theorem tot4686 : totK PA10K2 A10K2.t4686 = [0, 481627637272, 1780297326573, 2059996215915, 763967194612, 76422768762, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4687 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4687 = true := by
  decide +kernel

theorem tot4687 : totK PA10K2 A10K2.t4687 = [0, 317795168379, 1472756208202, 2158437589146, 976934102015, 81858830902, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
