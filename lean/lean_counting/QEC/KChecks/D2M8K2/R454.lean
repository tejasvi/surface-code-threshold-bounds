import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1816 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1816 = true := by
  decide +kernel

theorem tot1816 : totK PD2M8K2 D2M8K2.t1816 = [0, 0, 258303917320, 493678519590, 150846826694, 8417083954, 0, 0] := by
  decide +kernel

theorem rows1817 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1817 = true := by
  decide +kernel

theorem tot1817 : totK PD2M8K2 D2M8K2.t1817 = [0, 124262331957, 345395197531, 318718132387, 84989230950, 3455941720, 0, 0] := by
  decide +kernel

theorem rows1818 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1818 = true := by
  decide +kernel

theorem tot1818 : totK PD2M8K2 D2M8K2.t1818 = [0, 167506649714, 439023619823, 279443155895, 30408478054, 0, 0, 0] := by
  decide +kernel

theorem rows1819 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1819 = true := by
  decide +kernel

theorem tot1819 : totK PD2M8K2 D2M8K2.t1819 = [0, 108433287705, 389585877911, 318748044522, 54378784613, 1096156699, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
