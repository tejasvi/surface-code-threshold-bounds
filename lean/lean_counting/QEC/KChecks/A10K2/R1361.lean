import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5444 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5444 = true := by
  decide +kernel

theorem tot5444 : totK PA10K2 A10K2.t5444 = [0, 0, 606494053456, 1983694120585, 1905852412020, 506618926540, 27903531280, 0, 0, 0] := by
  decide +kernel

theorem rows5445 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5445 = true := by
  decide +kernel

theorem tot5445 : totK PA10K2 A10K2.t5445 = [0, 0, 0, 863307734536, 2438488483906, 1645829534536, 195038828956, 0, 0, 0] := by
  decide +kernel

theorem rows5446 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5446 = true := by
  decide +kernel

theorem tot5446 : totK PA10K2 A10K2.t5446 = [0, 131497176388, 318385760218, 501938553771, 1456660248702, 1868986966058, 651410165105, 42874818239, 0, 0] := by
  decide +kernel

theorem rows5447 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5447 = true := by
  decide +kernel

theorem tot5447 : totK PA10K2 A10K2.t5447 = [0, 453418298692, 1773028770593, 1958307419055, 555644145821, 32040661968, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
