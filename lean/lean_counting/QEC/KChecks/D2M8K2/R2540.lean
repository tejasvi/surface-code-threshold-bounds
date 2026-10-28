import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10160 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10160 = true := by
  decide +kernel

theorem tot10160 : totK PD2M8K2 D2M8K2.t10160 = [0, 162481956503, 478776431184, 261943037193, 14563925607, 0, 0, 0] := by
  decide +kernel

theorem rows10161 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10161 = true := by
  decide +kernel

theorem tot10161 : totK PD2M8K2 D2M8K2.t10161 = [0, 0, 202186085397, 463066404279, 221749379771, 21391863750, 0, 0] := by
  decide +kernel

theorem rows10162 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10162 = true := by
  decide +kernel

theorem tot10162 : totK PD2M8K2 D2M8K2.t10162 = [0, 0, 189053908051, 468522557124, 223304175607, 9392638393, 0, 0] := by
  decide +kernel

theorem rows10163 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10163 = true := by
  decide +kernel

theorem tot10163 : totK PD2M8K2 D2M8K2.t10163 = [0, 152968445628, 355325736287, 282003884748, 115333234922, 6804944647, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
