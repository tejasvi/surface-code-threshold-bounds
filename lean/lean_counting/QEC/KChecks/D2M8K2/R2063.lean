import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8252 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8252 = true := by
  decide +kernel

theorem tot8252 : totK PD2M8K2 D2M8K2.t8252 = [104995277616, 424079564848, 330200866522, 31250507434, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8253 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8253 = true := by
  decide +kernel

theorem tot8253 : totK PD2M8K2 D2M8K2.t8253 = [0, 274124001412, 512577012527, 108959116764, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows8254 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8254 = true := by
  decide +kernel

theorem tot8254 : totK PD2M8K2 D2M8K2.t8254 = [160315357794, 446412325283, 277188372040, 31802736888, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8255 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8255 = true := by
  decide +kernel

theorem tot8255 : totK PD2M8K2 D2M8K2.t8255 = [178220397277, 463998679934, 239103640192, 15273300119, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
