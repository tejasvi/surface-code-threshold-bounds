import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4264 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4264 = true := by
  decide +kernel

theorem tot4264 : totK PA10K2 A10K2.t4264 = [0, 0, 526111769267, 1836281116041, 1858317819005, 494138345619, 31112697984, 0, 0, 0] := by
  decide +kernel

theorem rows4265 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4265 = true := by
  decide +kernel

theorem tot4265 : totK PA10K2 A10K2.t4265 = [0, 0, 0, 799151994745, 2208619115409, 1497507472000, 260066619489, 7007974415, 0, 0] := by
  decide +kernel

theorem rows4266 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4266 = true := by
  decide +kernel

theorem tot4266 : totK PA10K2 A10K2.t4266 = [0, 0, 452062102207, 1746854074080, 1956079039968, 623211948146, 42531436804, 0, 0, 0] := by
  decide +kernel

theorem rows4267 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4267 = true := by
  decide +kernel

theorem tot4267 : totK PA10K2 A10K2.t4267 = [0, 0, 544553779586, 1935676320019, 1921711664417, 442211084982, 18093411651, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
