import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5380 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5380 = true := by
  decide +kernel

theorem tot5380 : totK PD2M8K2 D2M8K2.t5380 = [0, 0, 49142996948, 327545334439, 427457541301, 90969198117, 1242138600, 0] := by
  decide +kernel

theorem rows5381 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5381 = true := by
  decide +kernel

theorem tot5381 : totK PD2M8K2 D2M8K2.t5381 = [0, 0, 0, 222843425797, 469791572583, 162799391265, 7182288656, 0] := by
  decide +kernel

theorem rows5382 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5382 = true := by
  decide +kernel

theorem tot5382 : totK PD2M8K2 D2M8K2.t5382 = [0, 0, 126271388532, 338067652605, 288573184939, 130131645802, 13326740810, 0] := by
  decide +kernel

theorem rows5383 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5383 = true := by
  decide +kernel

theorem tot5383 : totK PD2M8K2 D2M8K2.t5383 = [0, 0, 183592416521, 451826484549, 221369602610, 10563779318, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
