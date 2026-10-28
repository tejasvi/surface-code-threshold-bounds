import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7780 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7780 = true := by
  decide +kernel

theorem tot7780 : totK PA10K2 A10K2.t7780 = [0, 449936922972, 1849012969576, 2006284306574, 500765551564, 25710589949, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7781 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7781 = true := by
  decide +kernel

theorem tot7781 : totK PA10K2 A10K2.t7781 = [0, 0, 752153441229, 2199365388048, 1512566262398, 217951810862, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows7782 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7782 = true := by
  decide +kernel

theorem tot7782 : totK PA10K2 A10K2.t7782 = [0, 0, 440707056174, 1823745408813, 1981655601433, 515542493035, 31987876949, 0, 0, 0] := by
  decide +kernel

theorem rows7783 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7783 = true := by
  decide +kernel

theorem tot7783 : totK PA10K2 A10K2.t7783 = [0, 0, 557027408346, 1868536193028, 1952883251055, 515989992651, 31529138169, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
