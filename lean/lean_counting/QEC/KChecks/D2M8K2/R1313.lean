import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5252 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5252 = true := by
  decide +kernel

theorem tot5252 : totK PD2M8K2 D2M8K2.t5252 = [0, 144995043752, 453238317928, 292795776034, 23305053919, 0, 0, 0] := by
  decide +kernel

theorem rows5253 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5253 = true := by
  decide +kernel

theorem tot5253 : totK PD2M8K2 D2M8K2.t5253 = [0, 0, 213147389666, 499252822565, 172717616004, 4961529011, 0, 0] := by
  decide +kernel

theorem rows5254 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5254 = true := by
  decide +kernel

theorem tot5254 : totK PD2M8K2 D2M8K2.t5254 = [0, 0, 195085723328, 456919518004, 219588320882, 17066492788, 0, 0] := by
  decide +kernel

theorem rows5255 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5255 = true := by
  decide +kernel

theorem tot5255 : totK PD2M8K2 D2M8K2.t5255 = [0, 0, 166300598128, 450782539034, 280025866616, 28472831638, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
