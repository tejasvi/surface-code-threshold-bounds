import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5356 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5356 = true := by
  decide +kernel

theorem tot5356 : totK PD2M8K2 D2M8K2.t5356 = [0, 180018194645, 462635215512, 251095172362, 23069299334, 0, 0, 0] := by
  decide +kernel

theorem rows5357 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5357 = true := by
  decide +kernel

theorem tot5357 : totK PD2M8K2 D2M8K2.t5357 = [0, 174795680566, 469488692555, 245679897769, 12624096550, 0, 0, 0] := by
  decide +kernel

theorem rows5358 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5358 = true := by
  decide +kernel

theorem tot5358 : totK PD2M8K2 D2M8K2.t5358 = [0, 0, 275366035522, 504850113811, 112653540559, 1198073392, 0, 0] := by
  decide +kernel

theorem rows5359 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5359 = true := by
  decide +kernel

theorem tot5359 : totK PD2M8K2 D2M8K2.t5359 = [0, 18567060971, 214562737953, 452169777243, 184661618881, 10583044771, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
