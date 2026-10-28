import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15224 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15224 = true := by
  decide +kernel

theorem tot15224 : totK PD2M8K2 D2M8K2.t15224 = [0, 0, 172622315890, 464203100630, 257602276285, 27824421967, 0, 0] := by
  decide +kernel

theorem rows15225 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15225 = true := by
  decide +kernel

theorem tot15225 : totK PD2M8K2 D2M8K2.t15225 = [0, 0, 174760730628, 451997531165, 258560282387, 18402922082, 0, 0] := by
  decide +kernel

theorem rows15226 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15226 = true := by
  decide +kernel

theorem tot15226 : totK PD2M8K2 D2M8K2.t15226 = [0, 0, 93518571537, 350005375816, 368433949639, 75820889578, 1242138600, 0] := by
  decide +kernel

theorem rows15227 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15227 = true := by
  decide +kernel

theorem tot15227 : totK PD2M8K2 D2M8K2.t15227 = [0, 0, 0, 255785195264, 474505180592, 140152703083, 4600645648, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
