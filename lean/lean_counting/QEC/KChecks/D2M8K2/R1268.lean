import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5072 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5072 = true := by
  decide +kernel

theorem tot5072 : totK PD2M8K2 D2M8K2.t5072 = [0, 138678414711, 444046799366, 278706886717, 19101848375, 0, 0, 0] := by
  decide +kernel

theorem rows5073 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5073 = true := by
  decide +kernel

theorem tot5073 : totK PD2M8K2 D2M8K2.t5073 = [0, 0, 268904163027, 514216253011, 98591260086, 1369150432, 0, 0] := by
  decide +kernel

theorem rows5074 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5074 = true := by
  decide +kernel

theorem tot5074 : totK PD2M8K2 D2M8K2.t5074 = [0, 133756414813, 398203069310, 343161341089, 43031678571, 0, 0, 0] := by
  decide +kernel

theorem rows5075 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5075 = true := by
  decide +kernel

theorem tot5075 : totK PD2M8K2 D2M8K2.t5075 = [0, 185559546136, 464198768587, 236219847869, 16971693599, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
