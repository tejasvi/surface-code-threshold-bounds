import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows92 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t92 = true := by
  decide +kernel

theorem tot92 : totK PD2M8K2 D2M8K2.t92 = [0, 175302544160, 446213367792, 259381241217, 27495399508, 0, 0, 0] := by
  decide +kernel

theorem rows93 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t93 = true := by
  decide +kernel

theorem tot93 : totK PD2M8K2 D2M8K2.t93 = [0, 199556739422, 472619318227, 214299839361, 14350423073, 0, 0, 0] := by
  decide +kernel

theorem rows94 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t94 = true := by
  decide +kernel

theorem tot94 : totK PD2M8K2 D2M8K2.t94 = [0, 176979634804, 466201763910, 247125905767, 19746127546, 0, 0, 0] := by
  decide +kernel

theorem rows95 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t95 = true := by
  decide +kernel

theorem tot95 : totK PD2M8K2 D2M8K2.t95 = [0, 174195913149, 467346159243, 241715729631, 13676787516, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
