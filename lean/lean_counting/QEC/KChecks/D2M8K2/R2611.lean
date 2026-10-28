import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10444 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10444 = true := by
  decide +kernel

theorem tot10444 : totK PD2M8K2 D2M8K2.t10444 = [0, 0, 0, 38122496643, 332138914271, 420937264432, 84528289290, 1171084559] := by
  decide +kernel

theorem rows10445 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10445 = true := by
  decide +kernel

theorem tot10445 : totK PD2M8K2 D2M8K2.t10445 = [0, 0, 0, 0, 195625788999, 459517124540, 185152571184, 11934365838] := by
  decide +kernel

theorem rows10446 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10446 = true := by
  decide +kernel

theorem tot10446 : totK PD2M8K2 D2M8K2.t10446 = [0, 0, 0, 168708100794, 457597631298, 232377944793, 19442664112, 0] := by
  decide +kernel

theorem rows10447 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10447 = true := by
  decide +kernel

theorem tot10447 : totK PD2M8K2 D2M8K2.t10447 = [0, 0, 0, 203956589201, 456033198401, 198490098974, 13404222388, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
