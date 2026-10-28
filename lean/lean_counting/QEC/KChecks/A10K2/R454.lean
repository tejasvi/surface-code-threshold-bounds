import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1816 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1816 = true := by
  decide +kernel

theorem tot1816 : totK PA10K2 A10K2.t1816 = [0, 0, 0, 267443090292, 1242523065946, 1887012042526, 1067128074735, 189679465909, 6034215561, 0] := by
  decide +kernel

theorem rows1817 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1817 = true := by
  decide +kernel

theorem tot1817 : totK PA10K2 A10K2.t1817 = [0, 0, 0, 569422931118, 1906515027178, 1759311885664, 445991187276, 31806683705, 0, 0] := by
  decide +kernel

theorem rows1818 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1818 = true := by
  decide +kernel

theorem tot1818 : totK PA10K2 A10K2.t1818 = [0, 0, 0, 0, 990410525646, 2387368182044, 1144777414998, 106115725275, 0, 0] := by
  decide +kernel

theorem rows1819 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1819 = true := by
  decide +kernel

theorem tot1819 : totK PA10K2 A10K2.t1819 = [0, 0, 0, 0, 471466120737, 1854307115843, 1742647823782, 462070973905, 31193230065, 0] := by
  decide +kernel

end QECKChecks.A10K2
