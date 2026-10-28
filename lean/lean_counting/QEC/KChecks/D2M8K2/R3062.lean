import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12248 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12248 = true := by
  decide +kernel

theorem tot12248 : totK PD2M8K2 D2M8K2.t12248 = [86093800102, 283210622291, 350748955081, 164449414361, 8036391702, 0, 0, 0] := by
  decide +kernel

theorem rows12249 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12249 = true := by
  decide +kernel

theorem tot12249 : totK PD2M8K2 D2M8K2.t12249 = [182382651690, 455302536302, 267516729371, 27719325365, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12250 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12250 = true := by
  decide +kernel

theorem tot12250 : totK PD2M8K2 D2M8K2.t12250 = [171260146135, 460352509067, 252135685738, 15017092468, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12251 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12251 = true := by
  decide +kernel

theorem tot12251 : totK PD2M8K2 D2M8K2.t12251 = [0, 265572624964, 508952984864, 125690881144, 2309606161, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
