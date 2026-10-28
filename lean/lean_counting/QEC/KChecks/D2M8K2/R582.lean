import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2328 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2328 = true := by
  decide +kernel

theorem tot2328 : totK PD2M8K2 D2M8K2.t2328 = [0, 0, 172376490713, 461613974015, 260208983002, 14260161032, 0, 0] := by
  decide +kernel

theorem rows2329 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2329 = true := by
  decide +kernel

theorem tot2329 : totK PD2M8K2 D2M8K2.t2329 = [0, 0, 92755880245, 430249313448, 360940801426, 36859442340, 0, 0] := by
  decide +kernel

theorem rows2330 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2330 = true := by
  decide +kernel

theorem tot2330 : totK PD2M8K2 D2M8K2.t2330 = [0, 0, 0, 235701136010, 501939410651, 138403500270, 2484078857, 0] := by
  decide +kernel

theorem rows2331 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2331 = true := by
  decide +kernel

theorem tot2331 : totK PD2M8K2 D2M8K2.t2331 = [0, 178250561612, 377095042706, 129750130807, 116621645357, 91378061266, 6818291842, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
