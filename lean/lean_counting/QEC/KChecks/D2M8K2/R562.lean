import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2248 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2248 = true := by
  decide +kernel

theorem tot2248 : totK PD2M8K2 D2M8K2.t2248 = [0, 172787991978, 465196613999, 244418145047, 13779823240, 0, 0, 0] := by
  decide +kernel

theorem rows2249 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2249 = true := by
  decide +kernel

theorem tot2249 : totK PD2M8K2 D2M8K2.t2249 = [0, 0, 281365896135, 491805830627, 112406183416, 1198073392, 0, 0] := by
  decide +kernel

theorem rows2250 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2250 = true := by
  decide +kernel

theorem tot2250 : totK PD2M8K2 D2M8K2.t2250 = [0, 18530029189, 189987299967, 455028410953, 192895462830, 12052611869, 0, 0] := by
  decide +kernel

theorem rows2251 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2251 = true := by
  decide +kernel

theorem tot2251 : totK PD2M8K2 D2M8K2.t2251 = [0, 182194454880, 464728516796, 247587775928, 22490689519, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
