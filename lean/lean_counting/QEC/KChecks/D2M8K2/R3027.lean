import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12108 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12108 = true := by
  decide +kernel

theorem tot12108 : totK PD2M8K2 D2M8K2.t12108 = [0, 0, 92362131504, 405044229910, 352006711849, 38652069542, 0, 0] := by
  decide +kernel

theorem rows12109 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12109 = true := by
  decide +kernel

theorem tot12109 : totK PD2M8K2 D2M8K2.t12109 = [0, 0, 241007453479, 471861748445, 182622370396, 10654524344, 0, 0] := by
  decide +kernel

theorem rows12110 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12110 = true := by
  decide +kernel

theorem tot12110 : totK PD2M8K2 D2M8K2.t12110 = [0, 0, 170408444729, 484246448093, 214639022873, 10629338089, 0, 0] := by
  decide +kernel

theorem rows12111 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12111 = true := by
  decide +kernel

theorem tot12111 : totK PD2M8K2 D2M8K2.t12111 = [0, 0, 181106544337, 462065186629, 253957169884, 22048831905, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
