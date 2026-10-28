import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1824 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1824 = true := by
  decide +kernel

theorem tot1824 : totK PD2M8K2 D2M8K2.t1824 = [0, 0, 225525070468, 494626439478, 170466561105, 5092263538, 0, 0] := by
  decide +kernel

theorem rows1825 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1825 = true := by
  decide +kernel

theorem tot1825 : totK PD2M8K2 D2M8K2.t1825 = [0, 0, 163222815810, 421485157568, 291360721794, 33939037411, 0, 0] := by
  decide +kernel

theorem rows1826 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1826 = true := by
  decide +kernel

theorem tot1826 : totK PD2M8K2 D2M8K2.t1826 = [0, 0, 204580223204, 486057088073, 214310590831, 10884817552, 0, 0] := by
  decide +kernel

theorem rows1827 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1827 = true := by
  decide +kernel

theorem tot1827 : totK PD2M8K2 D2M8K2.t1827 = [0, 0, 187816647536, 479318218240, 220225310619, 12308294887, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
