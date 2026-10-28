import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6840 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6840 = true := by
  decide +kernel

theorem tot6840 : totK PA10K2 A10K2.t6840 = [0, 0, 269918054631, 1331757804635, 1958507788566, 972626681647, 156469706135, 7007974415, 0, 0] := by
  decide +kernel

theorem rows6841 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6841 = true := by
  decide +kernel

theorem tot6841 : totK PA10K2 A10K2.t6841 = [0, 0, 485539712239, 1818939217913, 1936026592455, 509590500778, 23500939800, 0, 0, 0] := by
  decide +kernel

theorem rows6842 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6842 = true := by
  decide +kernel

theorem tot6842 : totK PA10K2 A10K2.t6842 = [0, 0, 497875188183, 1958402730406, 2141517268418, 574326987879, 19145700860, 0, 0, 0] := by
  decide +kernel

theorem rows6843 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6843 = true := by
  decide +kernel

theorem tot6843 : totK PA10K2 A10K2.t6843 = [0, 513260446086, 1769624736220, 1669604588166, 535860253896, 200970264220, 37674914273, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
