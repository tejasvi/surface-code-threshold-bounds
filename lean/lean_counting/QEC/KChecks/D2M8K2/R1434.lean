import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5736 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5736 = true := by
  decide +kernel

theorem tot5736 : totK PD2M8K2 D2M8K2.t5736 = [0, 204876572072, 466688772236, 222326909645, 19942028340, 0, 0, 0] := by
  decide +kernel

theorem rows5737 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5737 = true := by
  decide +kernel

theorem tot5737 : totK PD2M8K2 D2M8K2.t5737 = [0, 179323959169, 472966186990, 239696261801, 13842663846, 0, 0, 0] := by
  decide +kernel

theorem rows5738 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5738 = true := by
  decide +kernel

theorem tot5738 : totK PD2M8K2 D2M8K2.t5738 = [0, 0, 283230188590, 500301845276, 108986922688, 1232609433, 0, 0] := by
  decide +kernel

theorem rows5739 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5739 = true := by
  decide +kernel

theorem tot5739 : totK PD2M8K2 D2M8K2.t5739 = [0, 11364832707, 191802406899, 467405544943, 197971779827, 12482056447, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
