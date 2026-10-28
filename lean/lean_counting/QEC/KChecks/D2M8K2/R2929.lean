import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11716 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11716 = true := by
  decide +kernel

theorem tot11716 : totK PD2M8K2 D2M8K2.t11716 = [0, 182034145352, 452189717986, 237006606072, 18450603579, 0, 0, 0] := by
  decide +kernel

theorem rows11717 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11717 = true := by
  decide +kernel

theorem tot11717 : totK PD2M8K2 D2M8K2.t11717 = [0, 176554486752, 479244802584, 216259201824, 7984731767, 0, 0, 0] := by
  decide +kernel

theorem rows11718 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11718 = true := by
  decide +kernel

theorem tot11718 : totK PD2M8K2 D2M8K2.t11718 = [0, 125222935637, 430417621934, 295855171686, 22733488377, 0, 0, 0] := by
  decide +kernel

theorem rows11719 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11719 = true := by
  decide +kernel

theorem tot11719 : totK PD2M8K2 D2M8K2.t11719 = [0, 0, 279163723327, 498597204520, 89147058072, 1310285577, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
