import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1852 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1852 = true := by
  decide +kernel

theorem tot1852 : totK PA10K2 A10K2.t1852 = [0, 84348716664, 920546384828, 2152669328364, 1527910027416, 317325647896, 13561316338, 0, 0, 0] := by
  decide +kernel

theorem rows1853 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1853 = true := by
  decide +kernel

theorem tot1853 : totK PA10K2 A10K2.t1853 = [0, 420303068173, 1618944347727, 1964279333356, 828257938718, 87187441254, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1854 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1854 = true := by
  decide +kernel

theorem tot1854 : totK PA10K2 A10K2.t1854 = [0, 441902469423, 1760708446743, 2118950620308, 661978272298, 29939175074, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1855 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1855 = true := by
  decide +kernel

theorem tot1855 : totK PA10K2 A10K2.t1855 = [0, 0, 532887440265, 1942356474304, 1962679888047, 460486332409, 13816090359, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
