import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1800 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1800 = true := by
  decide +kernel

theorem tot1800 : totK PA10K2 A10K2.t1800 = [0, 0, 0, 0, 993665651806, 2412396603969, 1100238874563, 97901981758, 0, 0] := by
  decide +kernel

theorem rows1801 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1801 = true := by
  decide +kernel

theorem tot1801 : totK PA10K2 A10K2.t1801 = [0, 0, 0, 474201755587, 1480749882010, 1696062568759, 869804036058, 193557365844, 6354482628, 0] := by
  decide +kernel

theorem rows1802 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1802 = true := by
  decide +kernel

theorem tot1802 : totK PA10K2 A10K2.t1802 = [0, 0, 0, 335646020899, 1616533012616, 2115563441803, 671322901573, 39557919322, 0, 0] := by
  decide +kernel

theorem rows1803 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1803 = true := by
  decide +kernel

theorem tot1803 : totK PA10K2 A10K2.t1803 = [0, 0, 0, 0, 517635603888, 1877813328129, 1725962916719, 420354213022, 30388749007, 0] := by
  decide +kernel

end QECKChecks.A10K2
