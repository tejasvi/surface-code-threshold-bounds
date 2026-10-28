import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4192 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4192 = true := by
  decide +kernel

theorem tot4192 : totK PA10K2 A10K2.t4192 = [0, 509640231293, 1794896963364, 1882416143335, 529681896180, 31987755669, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4193 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4193 = true := by
  decide +kernel

theorem tot4193 : totK PA10K2 A10K2.t4193 = [0, 527152908723, 1956959510701, 1931168249965, 452521310916, 13149912228, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4194 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4194 = true := by
  decide +kernel

theorem tot4194 : totK PA10K2 A10K2.t4194 = [0, 453011119256, 1700187892043, 1989318639443, 649217015189, 39344277108, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4195 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4195 = true := by
  decide +kernel

theorem tot4195 : totK PA10K2 A10K2.t4195 = [0, 435397300521, 1736976304990, 1919207180268, 522535613626, 44363554315, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
