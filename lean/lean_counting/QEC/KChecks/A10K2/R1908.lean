import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7632 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7632 = true := by
  decide +kernel

theorem tot7632 : totK PA10K2 A10K2.t7632 = [0, 0, 0, 185950034399, 1181099352018, 2089475436435, 1245963093519, 200282011859, 6021244195, 0] := by
  decide +kernel

theorem rows7633 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7633 = true := by
  decide +kernel

theorem tot7633 : totK PA10K2 A10K2.t7633 = [0, 0, 0, 0, 599933790960, 2033351432885, 1871410445287, 388522158705, 11864432348, 0] := by
  decide +kernel

theorem rows7634 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7634 = true := by
  decide +kernel

theorem tot7634 : totK PA10K2 A10K2.t7634 = [0, 0, 448258699794, 1408206766263, 1377610914266, 621728548403, 627875308706, 372385158108, 43132710386, 0] := by
  decide +kernel

theorem rows7635 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7635 = true := by
  decide +kernel

theorem tot7635 : totK PA10K2 A10K2.t7635 = [0, 0, 423985901126, 1771110643411, 2074792682505, 639572307584, 26831101522, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
