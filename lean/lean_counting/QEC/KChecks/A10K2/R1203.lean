import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4812 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4812 = true := by
  decide +kernel

theorem tot4812 : totK PA10K2 A10K2.t4812 = [0, 447285710710, 1766432620299, 2074264959542, 630150155003, 41616068788, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4813 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4813 = true := by
  decide +kernel

theorem tot4813 : totK PA10K2 A10K2.t4813 = [0, 166332679591, 1098730999280, 2136211164296, 1357539675644, 230203461841, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows4814 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4814 = true := by
  decide +kernel

theorem tot4814 : totK PA10K2 A10K2.t4814 = [0, 0, 611149302810, 2088137189060, 1949794003316, 422620762097, 12855574250, 0, 0, 0] := by
  decide +kernel

theorem rows4815 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4815 = true := by
  decide +kernel

theorem tot4815 : totK PA10K2 A10K2.t4815 = [0, 0, 472404874239, 1733312865307, 2003455657785, 732584263276, 55772758487, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
