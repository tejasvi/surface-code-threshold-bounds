import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1768 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1768 = true := by
  decide +kernel

theorem tot1768 : totK PA10K2 A10K2.t1768 = [0, 0, 136853044638, 1320596997657, 2285582197115, 948100521695, 67345931770, 0, 0, 0] := by
  decide +kernel

theorem rows1769 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1769 = true := by
  decide +kernel

theorem tot1769 : totK PA10K2 A10K2.t1769 = [0, 0, 282936105235, 1172703777935, 1853117987567, 1205832972638, 233759675590, 6354482628, 0, 0] := by
  decide +kernel

theorem rows1770 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1770 = true := by
  decide +kernel

theorem tot1770 : totK PA10K2 A10K2.t1770 = [0, 0, 217158502480, 1242222597326, 2137470612325, 1293854053653, 223932093262, 6853348008, 0, 0] := by
  decide +kernel

theorem rows1771 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1771 = true := by
  decide +kernel

theorem tot1771 : totK PA10K2 A10K2.t1771 = [0, 0, 0, 524230453363, 1897969344358, 1948260191998, 511851460727, 31559907735, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
