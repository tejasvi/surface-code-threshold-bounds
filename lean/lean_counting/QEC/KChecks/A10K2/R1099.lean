import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4396 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4396 = true := by
  decide +kernel

theorem tot4396 : totK PA10K2 A10K2.t4396 = [0, 0, 314979364907, 1211975010769, 1819790313988, 1099697235031, 227545341017, 6354482628, 0, 0] := by
  decide +kernel

theorem rows4397 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4397 = true := by
  decide +kernel

theorem tot4397 : totK PA10K2 A10K2.t4397 = [0, 0, 516696083108, 1879480748922, 1918717524424, 457109240082, 11765040145, 0, 0, 0] := by
  decide +kernel

theorem rows4398 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4398 = true := by
  decide +kernel

theorem tot4398 : totK PA10K2 A10K2.t4398 = [0, 0, 0, 651805338693, 2019925490246, 1611339115873, 382211736569, 25371180993, 0, 0] := by
  decide +kernel

theorem rows4399 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4399 = true := by
  decide +kernel

theorem tot4399 : totK PA10K2 A10K2.t4399 = [0, 0, 287871761280, 1186410783559, 1881881548809, 1135953428869, 194126698644, 5447185874, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
